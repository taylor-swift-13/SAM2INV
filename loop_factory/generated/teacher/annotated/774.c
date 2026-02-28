int main1(int a,int k){
  int i, o, b, j;

  i=(k%30)+18;
  o=0;
  b=4;
  j=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant o == 0;
  loop invariant i == (\at(k,Pre) % 30) + 18;
  loop invariant i == ((\at(k, Pre) % 30) + 18);
  loop invariant i == (k % 30) + 18;
  loop invariant ( (b == 4 && j == -8) || (b == -14 && j == -6) || (b == 6 && j == 12) );
  loop invariant -14 <= b <= 6;
  loop invariant -8 <= j <= 12;
  loop assigns b, j;
*/
while (1) {
      b = b+1;
      j = j+1;
      b = b+1;
      j = j-1;
      b = j-b;
      j = j+o;
      j = b-j;
  }

}
