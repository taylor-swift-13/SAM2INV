int main1(int w){
  int esv, n, j;
  esv=w+11;
  n=0;
  j=w;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n >= 0;
  loop invariant j == w + n;
  loop invariant esv == w + 11;
  loop assigns j, n;
*/
while (1) {
      if (!(n<=esv-1)) {
          break;
      }
      j++;
      n += 1;
  }
}