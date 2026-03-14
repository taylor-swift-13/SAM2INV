int main1(int k,int h){
  int ah, p, a0, w8xs, itj, xfd;

  ah=(h%7)+11;
  p=0;
  a0=0;
  w8xs=0;
  itj=0;
  xfd=7;

  while (p<ah) {
      w8xs = p%5;
      if (!(!(p>=xfd))) {
          itj = (p-xfd)%5;
          a0 = a0+w8xs-itj;
      }
      else {
          a0 += w8xs;
      }
      p++;
      xfd = xfd+(p%2);
  }

}
