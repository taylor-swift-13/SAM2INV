int main1(){
  int i24l, e, oq, cr, b, akx, xue, p;

  i24l=(1%16)+11;
  e=0;
  oq=0;
  cr=0;
  b=0;
  akx=0;
  xue=0;
  p=0;

  while (1) {
      if (!(e<i24l+(1%7))) {
          break;
      }
      if (e%11==0) {
          oq += 1;
      }
      else {
          if (e%10==0) {
              cr = cr + 1;
          }
          else {
              if (e%2==0) {
                  b += 1;
              }
              else {
                  if (1) {
                      akx = akx + 1;
                  }
              }
          }
      }
      e += 1;
      xue += akx;
      p = p+e%2;
      xue += 1;
  }

}
