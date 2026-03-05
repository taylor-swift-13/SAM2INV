int main1(int n,int w){
  int uog, p1, g;
  uog=w+10;
  p1=3;
  g=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w >= \at(w, Pre);
  loop invariant uog == \at(w, Pre) + 10;
  loop invariant p1 == 3;
  loop invariant g == 0 || g == uog + 1;
  loop invariant (uog + 1 == 0) || ((w - \at(w, Pre)) % (uog + 1) == 0);
  loop invariant n == \at(n, Pre);
  loop assigns g, w;
*/
while (p1<uog) {
      g = uog-g;
      g++;
      w = w + g;
  }
}