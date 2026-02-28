int main1(int k,int q){
  int h, c, v, n;

  h=k-2;
  c=0;
  v=c;
  n=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == k - 2;

  loop invariant (k == \at(k, Pre));
  loop invariant (q == \at(q, Pre));
  loop invariant (h == k - 2);
  loop invariant (v == 0);
  loop invariant (0 <= c);
  loop invariant (h >= 0 ==> c <= h);
  loop invariant v == 0;

  loop invariant 0 <= c;
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);

  loop invariant c >= 0;
  loop assigns c, v;
*/
while (c<h) {
      v = v*v+v;
      c = c+1;
  }

}
