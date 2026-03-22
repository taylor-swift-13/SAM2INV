int main1(int j,int g){
  int ugu, f, mre;
  ugu=g;
  f=-9568;
  mre=ugu;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (j - f) - 4*mre == \at(j,Pre) + 9568 - 4*\at(g,Pre);
  loop invariant mre >= \at(g,Pre);
  loop invariant f == -9568 + ((mre - g) * (g + 2)) + (((mre - g) * ((mre - g) - 1)) / 2);
  loop invariant j == \at(j, Pre) + ((mre - g) * (g + 6)) + (((mre - g) * ((mre - g) - 1)) / 2);
  loop invariant 0 <= (mre - g);
  loop assigns f, j, mre;
*/
while (1) {
      if (!(f+7<0)) {
          break;
      }
      f = f+mre+2;
      mre = mre + 1;
      j += mre;
      j = j + 5;
  }
}