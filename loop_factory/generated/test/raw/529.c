int main1(){
  int iw, o, j, ted, pyz, ze3a;

  iw=1+19;
  o=0;
  j=0;
  ted=0;
  pyz=0;
  ze3a=0;

  while (o<iw) {
      if (!(!(o%11==0))) {
          if (o%8==0) {
              pyz++;
          }
          else {
              if (o%7==0) {
                  ted += 1;
              }
              else {
                  j++;
              }
          }
      }
      else {
          ze3a += 1;
      }
      o = o + 1;
      j++;
  }

}
