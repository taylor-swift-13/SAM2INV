int main1(int t,int b){
  int tbpu, w5h5, gjt, ou;

  tbpu=t-4;
  w5h5=0;
  gjt=1;
  ou=1;

  while (gjt<=tbpu) {
      w5h5 += 1;
      ou += 2;
      gjt += ou;
      t = t+(gjt%2);
  }

}
