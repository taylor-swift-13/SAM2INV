int main1(int a,int q){
  int n, w, h;

  n=q+10;
  w=0;
  h=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w >= 0;

  loop invariant h >= q;
  loop invariant h <= q + w;
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);

  loop invariant h - q <= w;
  loop invariant 0 <= w;
  loop invariant n == q + 10;
  loop invariant (a <= 0) ==> (h == q + w);
  loop invariant (h - q) <= w;
  loop invariant h - w <= q;
  loop assigns w, h;
*/
while (w<n) {
      if (a<w+1) {
          h = h+1;
      }
      w = w+1;
  }

}
