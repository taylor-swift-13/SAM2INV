int main1(int n,int q){
  int l, i, u, v;

  l=51;
  i=l;
  u=0;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u + i == l;
  loop invariant i % 4 == l % 4;
  loop invariant i >= 0;
  loop invariant u >= 0;
  loop invariant i + u == l;
  loop invariant i >= 3;
  loop invariant 0 <= u;
  loop invariant u <= l;
  loop invariant q == \at(q, Pre);
  loop invariant i % 4 == 3;
  loop invariant n == \at(n, Pre);
  loop invariant (i + u == l);
  loop invariant (u >= 0);
  loop invariant (i % 4 == 3);
  loop invariant (l == 51);
  loop invariant (i <= l);
  loop invariant (i + u) == 51;
  loop invariant (0 <= u);
  loop invariant (u <= 48);
  loop invariant ((i % 4) == 3);
  loop assigns i, u;
*/
while (i>3) {
      u = u+4;
      i = i-4;
  }

}
