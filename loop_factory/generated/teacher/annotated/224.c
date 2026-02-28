int main1(int p,int q){
  int k, i, x;

  k=q+14;
  i=0;
  x=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(q, Pre) + 14;
  loop invariant q == \at(q, Pre);
  loop invariant p == \at(p, Pre);

  loop invariant i > 0 ==> 0 <= x && x <= 25;
  loop invariant k == q + 14;

  loop invariant i >= 0;
  loop invariant (i == 0) ==> (x == k);
  loop invariant i == 0 || i <= k;
  loop invariant (i == 0 && x == k) || (i > 0 && (x == 0 || x == 1 || x == 4 || x == 9 || x == 16 || x == 25));
  loop invariant i == 0 ==> x == k;
  loop invariant i <= k || k < 0;

  loop invariant (i == 0) ==> (x == k) && (i > 0) ==> (0 <= x <= 25);
  loop assigns i, x;
*/
while (i<k) {
      x = x%6;
      x = x*x;
      i = i+1;
  }

}
