int main1(int a,int m){
  int b, u, i;

  b=69;
  u=3;
  i=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant i >= b;
  loop invariant (i + 6) % 75 == 0;
  loop invariant i >= 69;
  loop invariant (i + 6) % 3 == 0;
  loop invariant i % 3 == 0;
  loop invariant b == 69;
  loop invariant i >= -6;
  loop invariant i == 69 || i >= 144;
  loop invariant i >= 69 && a == \at(a, Pre) && m == \at(m, Pre);
  loop assigns i;
*/
while (1) {
      i = i+3;
      i = i+i;
  }

}
