int main1(int i,int m){
  int dd, uk7, qaf;
  dd=m;
  uk7=0;
  qaf=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qaf % 2 == 0;
  loop invariant i == \at(i, Pre);
  loop invariant dd == m;
  loop invariant 0 <= qaf;
  loop assigns qaf, i;
*/
while (qaf<dd) {
      if (qaf%8==0) {
          qaf = qaf + 1;
      }
      else {
          if (qaf%8==0) {
              qaf = qaf + 1;
          }
          else {
              if (qaf%5==0) {
                  qaf = qaf + 1;
              }
              else {
                  qaf = qaf + 1;
              }
          }
      }
      qaf = qaf + 1;
      i = i + uk7;
  }
}