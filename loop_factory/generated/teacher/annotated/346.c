int main1(int k,int m){
  int q, u, h, o;

  q=(k%10)+9;
  u=0;
  h=q;
  o=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant q <= h <= q+1;
  loop invariant h == q || h == q+1;
  loop invariant u <= q;
  loop invariant q == (k % 10) + 9;
  loop invariant u == 0;
  loop invariant h >= q;
  loop invariant h <= q + 1;
  loop invariant q <= h;
  loop invariant 0 <= u;
  loop assigns h;
*/
while (u<q) {
      if (h+6<=q) {
          h = h+6;
      }
      else {
          h = q;
      }
      h = h+1;
  }

}
