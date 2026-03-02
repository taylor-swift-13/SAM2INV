int main1(int k,int n){
  int b, i, v;

  b=(k%37)+9;
  i=0;
  v=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == (k % 37) + 9;
  loop invariant i >= 0;
  loop invariant v >= -4;
  loop invariant (i == 0) ==> (v == -4);
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant (i >= 1) ==> (v > 0);
  loop invariant i >= 0 && k == \at(k,Pre) && n == \at(n,Pre) && b == (\at(k,Pre) % 37) + 9;
  loop invariant b == (\at(k, Pre) % 37) + 9;
  loop invariant b == (k%37) + 9;
  loop invariant (i == 0) ==> v == -4 && (i >= 1) ==> v > 0;
  loop invariant (i > 0) ==> (v > 0);
  loop invariant k == \at(k, Pre) && n == \at(n, Pre) && b == (\at(k, Pre) % 37) + 9;
  loop invariant i >= 0 && v >= -4;
  loop assigns i, v;
*/
while (1) {
      v = v*v;
      i = i+1;
  }

}
