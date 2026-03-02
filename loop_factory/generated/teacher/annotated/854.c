int main1(int a,int k){
  int i, j, m;

  i=a+15;
  j=0;
  m=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == \at(a, Pre) + 15;
  loop invariant j == 0;
  loop invariant a == \at(a, Pre) && k == \at(k, Pre);

  loop invariant i == a + 15 && j == 0;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant i < 7 ==> ((m - a) % 4 == 0);
  loop invariant i == a + 15;


  loop invariant (a <= 5) ==> m >= a;
  loop invariant j == 0 && a == \at(a, Pre) && k == \at(k, Pre);

  loop assigns m;
*/
while (j+1<=i) {
      m = m+4;
      if (j+7<=j+i) {
          m = 5;
      }
  }

}
