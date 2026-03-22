int main1(int d,int h){
  int m4, n7, ep, cl, yo;

  m4=h*5;
  n7=2;
  ep=0;
  cl=n7;
  yo=0;

  while (ep<m4) {
      if (!(!(ep>=m4/2))) {
          cl += 4;
      }
      ep = ep + 1;
      yo = yo+cl-ep;
  }

}
