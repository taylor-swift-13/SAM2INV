int main1(int v){
  int v6, hp4r, at, ud;
  v6=36;
  hp4r=0;
  at=0;
  ud=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ud + hp4r == 3;
  loop invariant hp4r <= v6;
  loop invariant at == 3*hp4r - hp4r*(hp4r - 1)/2;
  loop invariant 0 <= ud;
  loop assigns at, hp4r, ud;
*/
while (1) {
      if (!(hp4r<v6&&ud>0)) {
          break;
      }
      at = at + ud;
      hp4r++;
      ud -= 1;
  }
}