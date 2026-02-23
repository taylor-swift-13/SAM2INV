int main1(int b,int k){
  int z, o, t;

  z=k-10;
  o=z+7;
  t=-3;

  while (o>=z+1) {
      t = t*t+t;
      if ((o%7)==0) {
          t = t*t+t;
      }
      o = o-3;
  }

}
