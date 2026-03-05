int main1(){
  int ep, n, eh;
  ep=(1%35)+7;
  n=ep;
  eh=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ep == 8;
  loop invariant eh == 2;
  loop invariant n == ep;
  loop invariant n > 3;
  loop assigns eh;
*/
while (n>3) {
      if (eh==1) {
          eh = 2;
      }
      else {
          if (eh==2) {
              eh = 1;
          }
      }
      eh++;
  }
}