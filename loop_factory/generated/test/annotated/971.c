int main1(int j,int x){
  int ws, c, yt;
  ws=(x%20)+5;
  c=(x%20)+5;
  yt=(x%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ws == c;
  loop invariant c == yt;
  loop invariant x >= \at(x,Pre);
  loop invariant ws <= ((\at(x,Pre) % 20) + 5);
  loop assigns ws, c, yt, x;
*/
while (ws>=1) {
      if (c>0) {
          if (yt>0) {
              ws--;
              c--;
              yt--;
          }
      }
      x = x + c;
  }
}