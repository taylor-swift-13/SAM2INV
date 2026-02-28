int main1(int a,int m,int n,int q){
  int b, h, w, r, u, o, v;

  b=18;
  h=1;
  w=q;
  r=a;
  u=m;
  o=a;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant w >= q;

  loop invariant r == a + ((w - q)/2) * q + ((w - q)/2) * ((w - q)/2);
  loop invariant ((w - q) % 2) == 0;
  loop invariant r == a + ((w - q)/2) * ((w - q)/2) + q * ((w - q)/2);
  loop invariant (w - q) >= 0;
  loop invariant r == a + ((w - q)/2) * (q + ((w - q)/2));
  loop invariant (w - q) % 2 == 0;
  loop invariant r == a + ((w - q) / 2) * (((w - q) / 2) + q);
  loop assigns w, r;
*/
while (1) {
      w = w+1;
      r = r+w;
      w = w+1;
  }

}
