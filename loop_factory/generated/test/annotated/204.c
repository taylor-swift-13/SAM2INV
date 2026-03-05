int main1(){
  int dfuj;
  dfuj=(1%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dfuj == 6;
  loop assigns dfuj;
*/
while (dfuj>0) {
      if (dfuj>0) {
          if (dfuj>0) {
              dfuj = dfuj - 1;
              dfuj = dfuj - 1;
              dfuj = dfuj - 1;
          }
      }
      dfuj = dfuj + dfuj;
  }
}