int main1(){
  int iaw, v4fb, yn;
  iaw=1+5;
  v4fb=iaw;
  yn=v4fb;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant iaw == 1 + 5;
  loop invariant ((yn == 6 && v4fb == 6) ||
                    (yn == 12 && v4fb == 3) ||
                    (yn == 24 && v4fb == 0));
  loop invariant (yn % 6 == 0);
  loop invariant (v4fb % 3 == 0);
  loop invariant 6 <= yn <= 24;
  loop invariant 0 <= v4fb <= 6;
  loop assigns yn, v4fb;
*/
while (1) {
      if (!(v4fb-3>=0)) {
          break;
      }
      yn = yn + yn;
      v4fb = v4fb - 3;
  }
}