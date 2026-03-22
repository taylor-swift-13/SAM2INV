int main1(){
  int mu9, wq, xx;
  mu9=32;
  wq=-2;
  xx=wq;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (xx == 0) || (xx == -2 && wq == -2);
  loop invariant wq <= mu9;
  loop assigns xx, wq;
*/
while (1) {
      if (!(wq<=mu9-1)) {
          break;
      }
      xx -= xx;
      wq++;
  }
}