int main1(){
  int d8c, hr2, wwd, nkq, m6;
  d8c=1;
  hr2=0;
  wwd=0;
  nkq=1;
  m6=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nkq == 1 + d8c * hr2;
  loop invariant wwd == hr2 + d8c * hr2 * (hr2 - 1) / 2;
  loop invariant m6  == hr2*(hr2+1)/2 + d8c * hr2*(hr2+1)*(hr2-1)/6;
  loop invariant 0 <= hr2 <= d8c;
  loop assigns wwd, m6, nkq, hr2;
*/
while (hr2 < d8c) {
      wwd += nkq;
      m6 += wwd;
      nkq = nkq + d8c;
      hr2++;
  }
}