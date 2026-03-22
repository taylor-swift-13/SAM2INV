int main1(){
  int u, y1, lb, yt, a, an;
  u=1*5;
  y1=-1;
  lb=(1%28)+8;
  yt=(1%22)+5;
  a=0;
  an=y1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lb > 0;
  loop invariant a >= 0;
  loop invariant an >= y1;
  loop invariant y1 + 1 <= an + u;
  loop invariant 0 <= yt <= 6;
  loop invariant lb % 9 == 0;
  loop invariant an >= -1;
  loop assigns a, lb, yt, an;
*/
while (yt!=0) {
      if (yt%2==1) {
          a += lb;
          yt--;
      }
      lb = 2*lb;
      yt = yt/2;
      an = an*3+(yt%4)+3;
      if (y1+1<=an+u) {
          an = an*an;
      }
  }
}