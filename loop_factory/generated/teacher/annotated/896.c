int main1(int b,int q){
  int n, t, k, u;

  n=q;
  t=0;
  k=q;
  u=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k - 3 <= u <= k && k >= q && (k - q) % 3 == 0 && u >= q;
  loop invariant k - 3 <= u <= k;
  loop invariant b == \at(b, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant n == q;
  loop invariant (k - q) % 3 == 0;
  loop invariant (k - u) % 3 == 0;
  loop invariant u <= k;
  loop invariant k - u == 0 || k - u == 3;
  loop invariant 0 <= k - u;
  loop invariant k >= q;
  loop invariant u >= q;
  loop invariant (u == k) || (u == k - 3);
  loop invariant (k - u == 0) || (k - u == 3);
  loop invariant b == \at(b,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant k - u <= 3;
  loop invariant n == \at(q, Pre);
  loop invariant k >= u;
  loop assigns u, k;
*/
while (1) {
      u = k;
      k = k+3;
  }

}
