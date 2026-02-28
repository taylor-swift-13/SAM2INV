int main1(int p,int q){
  int r, u, v;

  r=(q%29)+5;
  u=0;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == (q % 29) + 5;
  loop invariant 0 <= u;
  loop invariant (v == q) || (v == 0);
  loop invariant (u == 0) ==> (v == q);

  loop invariant v == 0 || v == q;
  loop invariant r == (\at(q, Pre) % 29) + 5;
  loop invariant (r >= 1) ==> (0 <= u && u <= r);
  loop invariant (r >= 1) ==> (u <= r);
  loop invariant (0 <= u) && (v == q || v == 0);
  loop invariant q == \at(q, Pre);

  loop invariant v == \at(q, Pre) || v == 0;
  loop assigns u, v;
*/
while (u<=r-1) {
      if (v<r+4) {
          v = v-v;
      }
      u = u+1;
  }

}
