int main1(){
  int jq7, b, zjpo;
  jq7=0;
  b=(1%28)+10;
  zjpo=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zjpo == jq7*(jq7+1)/2;
  loop invariant b >= 0;
  loop invariant b == 11 - jq7*(jq7 - 1)/2;
  loop invariant 0 <= jq7;
  loop assigns b, jq7, zjpo;
*/
while (1) {
      if (!(b>jq7)) {
          break;
      }
      b -= jq7;
      jq7 = (1)+(jq7);
      zjpo += jq7;
  }
}