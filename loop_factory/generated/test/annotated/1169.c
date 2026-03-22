int main1(){
  int x, ak, ifd, rb, w;
  x=1*2;
  ak=0;
  ifd=1;
  rb=1;
  w=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rb == 2*ak + 1;
  loop invariant ifd == (ak + 1) * (ak + 1);
  loop invariant w == ak * (3*ak + 5) / 2;
  loop invariant ak >= 0;
  loop invariant ak <= 1;
  loop assigns ak, rb, w, ifd;
*/
while (1) {
      if (!(ifd<=x)) {
          break;
      }
      ak = ak + 1;
      rb += 2;
      w = w+rb+ak;
      ifd += rb;
  }
}