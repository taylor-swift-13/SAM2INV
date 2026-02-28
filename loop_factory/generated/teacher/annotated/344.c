int main1(int b,int k){
  int v, i, j, p;

  v=70;
  i=v;
  j=-5;
  p=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 70;
  loop invariant p == -5;
  loop invariant j <= v;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant (j + 5) % 8 == 0;
  loop invariant v - j >= 75;
  loop assigns j;
*/
while (j<v) {
      if (j<v) {
          j = j+1;
      }
      j = j+p+p;
      j = j+1;
  }

}
