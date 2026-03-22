int main1(){
  int wc6o, sl5t, ogsm, ga;
  wc6o=(1%18)+18;
  sl5t=(1%40)+2;
  ogsm=0;
  ga=wc6o;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ga >= 19;
  loop invariant ogsm + sl5t <= wc6o;
  loop invariant 0 <= ogsm <= 4;
  loop invariant ga >= wc6o;
  loop invariant ogsm <= ga - wc6o;
  loop invariant ogsm <= sl5t;
  loop invariant (sl5t == 3) || (sl5t == 4);
  loop assigns ga, ogsm, sl5t;
*/
while (sl5t!=ogsm) {
      ogsm = sl5t;
      ga += ogsm;
      sl5t = (sl5t+wc6o/sl5t)/2;
  }
}