int main1(int i,int m){
  int dd, uk7, qaf;

  dd=m;
  uk7=0;
  qaf=0;

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
