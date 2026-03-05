int main1(){
  int rz, x, c;
  rz=1+8;
  x=rz;
  c=(1%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rz == 9;
  loop invariant c == 9;
  loop invariant x >= 9;
  loop assigns c, x;
*/
while (c>0&&c>0) {
      if (x%2==0) {
          c--;
      }
      else {
          c--;
      }
      x = x + 1;
      c = c + 1;
  }
}