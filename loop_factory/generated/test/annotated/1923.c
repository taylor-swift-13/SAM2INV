int main1(){
  int p, vq, s1, h76, wy, v3f, eh, l;
  p=1+7;
  vq=2;
  s1=7;
  h76=0;
  wy=vq;
  v3f=8;
  eh=p;
  l=vq;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (s1 + h76 == 7);
  loop invariant (wy == vq);
  loop invariant v3f >= 8;
  loop invariant eh >= p;
  loop invariant l >= 2;
  loop invariant (l % 2) == 0;
  loop invariant eh >= 8;
  loop invariant (0 <= s1 && s1 <= 7);
  loop invariant (0 <= h76 && h76 <= 7);
  loop invariant (2 <= vq && vq <= p);
  loop assigns s1, h76, wy, vq, eh, v3f, l;
*/
while (vq<p) {
      if (!(!(vq%2==0))) {
          if (s1>0) {
              s1 = s1 - 1;
              h76 = h76 + 1;
          }
      }
      else {
          if (h76>0) {
              h76--;
              s1 += 1;
          }
      }
      wy = wy + 1;
      vq = vq + 1;
      eh = eh + h76;
      v3f += wy;
      if (vq+2<=v3f+p) {
          l += 2;
      }
      else {
          v3f = v3f + eh;
      }
  }
}