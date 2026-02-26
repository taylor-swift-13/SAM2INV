int main1(int a,int m){
  int l, v, i;

  l=(a%18)+15;
  v=0;
  i=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant l == (a % 18) + 15;
  loop invariant i <= 0;
  loop invariant i >= -5;
  loop invariant i == -5 || i == 0;
  loop invariant (i == -5 || i == 0);
  loop invariant l == (\at(a, Pre) % 18) + 15;
  loop assigns i;
*/
while (1) {
      i = i+3;
      i = i-i;
  }

}
