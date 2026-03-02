int main1(int b,int q){
  int n, u, v, h;

  n=38;
  u=0;
  v=q;
  h=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= u;
  loop invariant u <= n;
  loop invariant n == 38;
  loop invariant b == \at(b, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant u == 0;
  loop invariant n == 38 && u <= n && q == \at(q, Pre) && b == \at(b, Pre);
  loop invariant ((u == 0 && v == q && h == q) || (v == 3*h + 2));
  loop invariant u == 0 && n == 38 && b == \at(b, Pre);
  loop invariant (v == 3*h + 2) || (h == \at(q, Pre) && v == \at(q, Pre));
  loop invariant u <= n && n == 38;
  loop assigns h, v;
*/
while (u<n) {
      h = v;
      v = v+2;
      v = v+h+h;
  }

}
