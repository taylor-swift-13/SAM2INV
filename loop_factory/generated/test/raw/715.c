int main1(){
  int jnm, t, ot, u;

  jnm=1+14;
  t=(1%40)+2;
  ot=0;
  u=0;

  while (t!=ot) {
      ot = t;
      t = (t+jnm/t)/2;
      u = u+t-t;
  }

}
