int main1(){
  int xgnr, v4, p, t2, mga, akah;

  xgnr=1+22;
  v4=0;
  p=13;
  t2=0;
  mga=1;
  akah=0;

  while (p>0&&v4<xgnr) {
      if (p<=mga) {
          akah = p;
      }
      else {
          akah = mga;
      }
      t2 = t2 + akah;
      mga = mga + 1;
      p = p - akah;
      v4 += 1;
  }

}
