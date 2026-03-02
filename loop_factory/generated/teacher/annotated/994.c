int main1(int k,int n){
  int b, i, v;

  b=(k%37)+9;
  i=0;
  v=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(k, Pre) % 37 + 9 && k == \at(k, Pre) && n == \at(n, Pre);
  loop invariant i >= 0;
  loop invariant b == \at(k, Pre) % 37 + 9;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant (v + 2*i + 2) < 0 && v % 2 == 0;
  loop invariant v % 2 == 0;
  loop invariant v <= -2*i - 4;
  loop invariant v + 2*i + 2 <= -2;
  loop assigns v, i;
*/
while (1) {
      v = v+i;
      v = v+v;
      i = i+1;
  }

}
