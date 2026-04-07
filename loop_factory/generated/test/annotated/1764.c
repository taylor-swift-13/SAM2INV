int main1(){
  int t6, ncq7, a3, osiq;
  t6=(1%24)+16;
  ncq7=1;
  a3=t6;
  osiq=ncq7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ncq7 == 1;
  loop invariant a3 == 16 + osiq*(osiq+1)*(2*osiq+1)*(3*osiq*osiq + 3*osiq - 1)/30;
  loop invariant osiq >= 1;
  loop invariant t6 >= 3;
  loop invariant t6 <= 17;
  loop assigns osiq, a3, t6;
*/
while (1) {
      if (!(ncq7*4<=t6)) {
          break;
      }
      osiq = osiq + 1;
      a3 = a3+osiq*osiq*osiq*osiq;
      t6 = (ncq7*4)-1;
  }
}