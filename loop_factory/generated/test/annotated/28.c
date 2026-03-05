int main1(int e){
  int j, ri;
  j=e+16;
  ri=-7659;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == \at(e, Pre) + 16 && (ri == -7659 || ri % 2 == 0);
  loop invariant ri <= -7659;
  loop assigns ri, e;
*/
while (ri+4<0) {
      ri = ri+ri-3;
      ri = ri + 3;
      e += j;
  }
}