"""Compile only the source ZIP in a new temporary workspace and record results."""
from pathlib import Path
import tempfile,zipfile,subprocess,json,hashlib,re,shutil
r=Path(__file__).resolve().parents[1]
tmp=Path(tempfile.mkdtemp(prefix='zagreb-arxiv-zip-'))
with zipfile.ZipFile(r/'arxiv-source.zip') as z:
    assert sorted(z.namelist())==['main.bbl','main.tex','references.bib']
    assert z.testzip() is None
    z.extractall(tmp)
steps=[]
for i,args in enumerate([
 ['pdflatex','-interaction=nonstopmode','-halt-on-error','main.tex'],
 ['bibtex','main'],
 ['pdflatex','-interaction=nonstopmode','-halt-on-error','main.tex'],
 ['pdflatex','-interaction=nonstopmode','-halt-on-error','main.tex']]):
    p=subprocess.run(args,cwd=tmp,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (r/'validation'/('zip-build-'+str(i+1)+'.txt')).write_text(p.stdout)
    steps.append({'command':' '.join(args),'exit_code':p.returncode})
    assert p.returncode==0,p.stdout[-3000:]
log=(tmp/'main.log').read_text()
assert not re.search(r'Warning|Overfull|Underfull|Missing character|^!',log,re.M)
for pdf,txt in [(tmp/'main.pdf',tmp/'main.txt'),(r/'main.pdf',r/'build/main.txt')]:
    subprocess.run(['pdftotext','-layout',str(pdf),str(txt)],check=True)
assert (tmp/'main.txt').read_bytes()==(r/'build/main.txt').read_bytes()
assert (tmp/'main.bbl').read_bytes()==(r/'main.bbl').read_bytes()
text=(r/'build/main.txt').read_text()
assert '0009-0000-4898-0333' in text
assert 'Independent Researcher' in text
assert 'Disclosure of generative-AI assistance' in text
repo=r.parents[1]
def git(*args): return subprocess.check_output(['git','-C',str(repo),*args],text=True)
assert not git('diff','--name-only').strip()
assert not git('diff','--cached','--name-only').strip()
audit='68a494573fdbd2e629c620a263dafed5853ac26e'
paths=[p for p in git('ls-files','*.lean').splitlines()]
paths+=['lean-toolchain','lakefile.toml','lake-manifest.json']
assert not git('diff',audit,'HEAD','--',*paths).strip()
subprocess.run(['git','-C',str(repo),'diff','--check'],check=True)
fontinfo=subprocess.check_output(['pdffonts',str(r/'main.pdf')],text=True)
(r/'validation/fonts.txt').write_text(fontinfo)
assert all(re.search(r'yes\s+yes\s+yes',line) for line in fontinfo.splitlines()[2:])
summary={'status':'PASS','pages':text.count('\f'),'zip_files':['main.tex','references.bib','main.bbl'],
'clean_zip_build':steps,'clean_zip_text_matches_delivered_pdf':True,'bibliography_rebuild_matches':True,
'final_latex_warnings':[],'unresolved_citations_or_references':False,'all_fonts_embedded':True,
'author_orcid_and_disclosure_present':True,'existing_tracked_files_modified':False,
'lean_and_pins_match_audited_commit':True,'repository_HEAD':git('rev-parse','HEAD').strip(),
'clean_zip_workspace':str(tmp),'toolchain':subprocess.check_output(['pdflatex','--version'],text=True).splitlines()[0],
'files_sha256':{n:hashlib.sha256((r/n).read_bytes()).hexdigest() for n in ['main.tex','references.bib','main.bbl','main.pdf','arxiv-source.zip']}}
(r/'validation/build-results.json').write_text(json.dumps(summary,indent=2)+'\n')
shutil.copyfile(r/'build/main.log',r/'validation/final-latex.log')
shutil.copyfile(r/'build/bibtex.txt',r/'validation/final-bibtex.txt')
print(json.dumps(summary,indent=2))
