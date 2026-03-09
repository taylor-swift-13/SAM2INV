int main1(int w){
  int a3l, yp, it;
  a3l=w*2;
  yp=0;
  it=a3l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a3l == 2 * \at(w, Pre);
  loop invariant w == \at(w, Pre) + yp*(yp+1)/2;
  loop invariant (yp > 0)  ==> (it == a3l - yp + 1);
  loop invariant (a3l > 0) ==> (0 <= yp && yp <= a3l);
  loop assigns w, yp, it;
*/
while (1) {
      if (!(yp<a3l)) {
          break;
      }
      it = a3l-yp;
      yp += 1;
      w = w + yp;
  }
}