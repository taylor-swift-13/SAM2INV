/*@ requires A >= 1 && (R-1)*(R-1) < A && A <= R*R && A%2 ==1;*/
int main1(){

  int u, v, r, A, R;
  
  u=2*R+1;
  v=1;
  r=R*R-A;

  while(r>0) {
    r=r-v;
    v=v+2;
  }
  /*@ assert 4*(A+r) == u*u-v*v-2*u+2*v;*/
}

