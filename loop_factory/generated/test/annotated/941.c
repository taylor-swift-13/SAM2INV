int main1(){
  int mft4, n, fo, ycr;
  mft4=1;
  n=mft4;
  fo=(1%20)+10;
  ycr=(1%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fo >= 0;
  loop invariant ycr >= 0;
  loop invariant n >= 1;
  loop invariant fo + ycr + n == 21;
  loop invariant fo <= 11;
  loop invariant ycr <= 9;
  loop invariant mft4 == 1;
  loop assigns fo, ycr, n;
*/
while (fo>0&&ycr>0) {
      if (!(!(n%2==0))) {
          fo--;
      }
      else {
          ycr -= 1;
      }
      n += 1;
  }
}