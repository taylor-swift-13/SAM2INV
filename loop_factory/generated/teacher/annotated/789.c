int main1(int k,int m){
  int r, i, b;

  r=(k%29)+12;
  i=0;
  b=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i >= 0;
  loop invariant r == (\at(k, Pre) % 29) + 12;
  loop invariant (i == 0) ==> (b == -8);
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant (i >= 0);
  loop invariant (k == \at(k, Pre));
  loop invariant (m == \at(m, Pre));
  loop invariant r == ((\at(k, Pre) % 29) + 12);
  loop invariant (i == 0 && b == -8) || (i >= 1 && b == 0);
  loop assigns b, i;
*/
while (1) {
      if ((i%6)==0) {
          b = b-b;
      }
      else {
          b = b-b;
      }
      b = b+b;
      i = i+1;
  }

}
