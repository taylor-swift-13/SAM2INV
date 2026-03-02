int main1(int n,int q){
  int u, v, c, i;

  u=50;
  v=u;
  c=q;
  i=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == 50 && i == n && v >= 50;
  loop invariant v <= u && c == q + (v - 50) * 2 * (i + 1);
  loop invariant u == 50 && n == \at(n, Pre) && i == n;
  loop invariant c - 2*(v - 50)*(i + 1) == \at(q, Pre) && 50 <= v && v <= u;
  loop invariant c == q + (v - u) * 2 * (i + 1) && v <= u;
  loop invariant i == n;
  loop invariant c == q + 2 * (i + 1) * (v - 50);
  loop invariant c == q + 2*(i+1)*(v - 50);
  loop invariant v <= u;
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant (v <= u);
  loop invariant (i == n);
  loop invariant (q == \at(q, Pre));
  loop invariant (n == \at(n, Pre));
  loop invariant ((c - q) == (v - u) * (2 + 2*i));
  loop invariant c - q == 2*(i+1)*(v - 50) && i == n;
  loop invariant u == 50 && v <= u && v >= 50;
  loop invariant v <= u && c == q + (v - 50) * (2 + 2*i);
  loop invariant c == q + (v - 50) * (2 + 2 * i);
  loop invariant c == q + 2*(i+1)*(v - u);
  loop invariant (v - u) >= 0;
  loop invariant (c - q) % 2 == 0;
  loop assigns c, v;
*/
while (1) {
      if (v>=u) {
          break;
      }
      c = c+2;
      v = v+1;
      c = c+i+i;
  }

}
