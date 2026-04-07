int main1(int f){
  int cl, w, d, uu3, ns;
  cl=f;
  w=0;
  d=0;
  uu3=2;
  ns=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= d <= 1;
  loop invariant uu3 == 2 + d;
  loop invariant ns == 2*d + d*(d+1)*(d+2)/6;
  loop invariant (d > 0) ==> (w == cl);
  loop invariant w >= 0;
  loop invariant cl == f;
  loop assigns d, uu3, ns, w;
*/
while (w<cl) {
      d++;
      uu3 += d;
      ns = ns + uu3;
      w = cl;
  }
}