int main1(int k,int m){
  int i, h, s;

  i=45;
  h=0;
  s=h;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s % 4 == 0;
  loop invariant s >= 0;
  loop invariant i == 45;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop assigns s;
*/
while (1) {
      s = s+2;
      s = s+s;
  }

}
