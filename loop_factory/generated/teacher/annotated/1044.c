int main1(int k,int m){
  int r, b, c;

  r=m+5;
  b=0;
  c=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == \at(m, Pre) + 5 && k == \at(k, Pre) && m == \at(m, Pre) && b >= 0;
  loop invariant c >= 6 && c % 6 == 0;
  loop invariant r == \at(m, Pre) + 5;
  loop invariant m == \at(m, Pre) && k == \at(k, Pre);
  loop invariant b >= 0;
  loop invariant c > 0 && c % 6 == 0;
  loop invariant r == \at(m, Pre) + 5 && k == \at(k, Pre) && m == \at(m, Pre);
  loop invariant b >= 0 && c >= 6 && c % 6 == 0;
  loop invariant r == \at(m, Pre) + 5 && m == \at(m, Pre) && k == \at(k, Pre);
  loop invariant b >= 0 && c % 6 == 0 && c >= 6;
  loop invariant r == \at(m, Pre) + 5 && m == \at(m, Pre) && k == \at(k, Pre) && b >= 0;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant 0 <= b % 8 && b % 8 <= 7;
  loop invariant c % 6 == 0 && c >= 6;
  loop invariant c >= 6;
  loop invariant c % 6 == 0;
  loop assigns b, c;
*/
while (1) {
      if ((b%8)==0) {
          c = c+c;
      }
      b = b+1;
  }

}
