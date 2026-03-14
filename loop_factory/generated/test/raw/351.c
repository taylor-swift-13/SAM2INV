int main1(int q){
  int yc, p, d, ur;

  yc=0;
  p=0;
  d=0;
  ur=(q%18)+5;

  while (ur>0) {
      d = d+q*q;
      yc = yc+q*q;
      ur--;
      p = p+q*q;
      q += yc;
  }

  while (d>yc) {
      d -= yc;
      yc = (1)+(yc);
      q += p;
  }

}
