int main1(){
  int x, y, r, kg, atll, a;

  x=1+15;
  y=0;
  r=0;
  kg=0;
  atll=0;
  a=0;

  while (1) {
      if (!(y<x)) {
          break;
      }
      if (!(!(y%9==0))) {
          if (y%6==0) {
              atll = atll + 1;
          }
          else {
              if (y%7==0) {
                  kg = kg + 1;
              }
              else {
                  r = r + 1;
              }
          }
      }
      else {
          a++;
      }
      r = r + 1;
      y++;
  }

}
