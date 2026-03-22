int main1(int r){
  int svq, w, hz96, ls;
  svq=168;
  w=(r%40)+2;
  hz96=0;
  ls=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hz96 != 0 ==> w == (hz96 + svq/hz96)/2;
  loop assigns hz96, w, ls;
*/
while (1) {
      if (!(w!=hz96)) {
          break;
      }
      hz96 = w;
      w = (w+svq/w)/2;
      ls = ls+(w%5);
  }
}