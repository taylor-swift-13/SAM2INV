int main1(){
  int rbu, aof, fa, i;
  rbu=20;
  aof=0;
  fa=10;
  i=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant aof == i;
  loop invariant fa == 10;
  loop invariant rbu == 20;
  loop invariant 0 <= i <= rbu;
  loop assigns aof, i, fa;
*/
while (1) {
      if (!(aof < rbu)) {
          break;
      }
      aof++;
      fa = (fa)+(-(1));
      i = i + 1;
      fa++;
  }
}