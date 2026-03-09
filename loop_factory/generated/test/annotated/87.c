int main1(){
  int js, vft, i, vh;
  js=1+3;
  vft=-5;
  i=0;
  vh=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= vh;
  loop invariant vh <= js;
  loop invariant vft == -5;
  loop invariant js == 4;
  loop invariant i <= 0;
  loop invariant i % 4 == 0;
  loop invariant ((i - (vft + 1) * vh) % 8) == 0;
  loop assigns i, vh;
*/
while (vh<js) {
      i = (i+1)%8;
      vh = vh + 1;
      i += vft;
  }
}