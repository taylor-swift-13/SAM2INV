int main1(int v,int f){
  int rb, o0c, un, pfw, yq, r1, cn, jfj;
  rb=f;
  o0c=0;
  un=25;
  pfw=12;
  yq=0;
  r1=o0c;
  cn=12;
  jfj=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == \at(f, Pre);
  loop invariant rb == \at(f, Pre);
  loop invariant (rb < 0) || (0 <= o0c && o0c <= rb);
  loop invariant yq == v - \at(v, Pre);
  loop invariant jfj >= 3;
  loop invariant 0 <= r1;
  loop invariant 12 <= pfw;
  loop invariant pfw <= 12 + o0c;
  loop invariant o0c >= 0;
  loop invariant (r1 + jfj) == (o0c + 3);
  loop invariant yq >= 0;
  loop assigns o0c, un, pfw, r1, jfj, v, yq, cn;
*/
while (o0c < rb) {
      o0c = o0c + 1;
      un = (v + f + o0c) % rb;
      if ((un == 0)) {
          pfw = pfw + 1;
      }
      if ((un % 2 == 0)) {
          r1++;
      }
      else {
          jfj += 1;
      }
      v += jfj;
      yq += jfj;
      cn = cn + 3;
      cn += v;
  }
}