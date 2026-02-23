int main1(int a,int p){
  int k, j, v;

  k=52;
  j=k;
  v=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (j >= 0) && (j <= k);
  loop invariant (a == \at(a, Pre)) && (p == \at(p, Pre)) && (k == 52) && ((v == a + 9) || (j == 52 && v == -8));
  loop invariant (0 <= j) && (j <= 52);
  loop invariant k == 52;
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant 0 <= j && j <= k;
  loop invariant (j == k && v == -8) || (j < k && v == a + 9);
  loop invariant 0 <= j;
  loop invariant j <= 52;
  loop invariant 0 <= j <= 52;
  loop assigns j, v;
*/
while (j>0) {
      v = a+8;
      v = v+1;
      j = j-1;
  }

}
