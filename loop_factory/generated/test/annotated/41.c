int main1(int s,int z,int w){
  int uf, yq, hvs, rn4s;
  uf=s+24;
  yq=0;
  hvs=z;
  rn4s=w;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == \at(s, Pre) + uf * yq;
  loop invariant hvs == \at(z, Pre) + 3 * yq;
  loop invariant rn4s == \at(w, Pre) + yq;
  loop invariant uf == \at(s, Pre) + 24;
  loop invariant s == \at(s, Pre) + yq * uf;
  loop invariant 0 <= yq;
  loop invariant hvs - 3*yq == z;
  loop invariant rn4s == w + yq;
  loop invariant hvs == z + 3*yq;
  loop invariant yq >= 0;
  loop assigns hvs, yq, s, rn4s;
*/
while (1) {
      if (yq>=uf) {
          break;
      }
      hvs = hvs + 3;
      yq = yq + 1;
      s = s + uf;
      rn4s++;
  }
}