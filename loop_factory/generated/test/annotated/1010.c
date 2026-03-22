int main1(){
  int xgnr, v4, p, t2, mga, akah;
  xgnr=1+22;
  v4=0;
  p=13;
  t2=0;
  mga=1;
  akah=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mga == v4 + 1;
  loop invariant 0 <= p;
  loop invariant 0 <= t2;
  loop invariant v4 <= xgnr;
  loop invariant p + t2 == 13;
  loop invariant 1 <= mga;
  loop assigns akah, p, t2, mga, v4;
*/
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